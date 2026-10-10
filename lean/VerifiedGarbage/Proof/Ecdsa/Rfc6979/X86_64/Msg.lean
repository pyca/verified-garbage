import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Blocks
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce

/-!
# Deterministic ECDSA on x86-64: the messages of steps d, f and h.3

`V ‖ b`, and `‖ d ‖ h` if `full`, at `scratch + 2256`, for `V` of `D` bytes
(`msg_ok`): `V` copied from the frame (`head_ok`), the byte `b`, then the
private key and `h` copied (`tail_ok`), or, if `wide`, the private key, a
zero word and the digest, which leaves `h` as `Q - D` zero bytes then the
digest (`tailW_ok`).
-/

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
  WP.mono_syms (copyN_ok (K := K) (by decide) hsr hsep (by have := hL.nc; omega_arith) K (Nat.le_refl _) u hs hdi hr
    fun j hj => hc.inScrW (by omega_arith)) fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy =>
    ⟨hc.keep hL hrd hwr (hg _ (by decide)) (fun r hr _ => hg r (ne_cs hr (by decide))) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L hd) hsy,
      hrd, hwr, hg, hf, hb⟩

theorem fr_add (B : Addr) (o : Nat) : B + BitVec.ofNat 64 24 + BitVec.ofNat 64 o = B + BitVec.ofNat 64 (24 + o) :=
  Offset.add_add _ _ _

/-- The pointers: `scratch` in `rdi`, `d` in `rsi`, and, if `wide`, `digest` in `rdx`. -/
theorem ptrs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (wide : Bool) :
    WP isa (.block (Cfg.msgPtrs wide)) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .rdi = L.scr ∧
      u.gpr .rsi = L.d ∧ (wide = true → u.gpr .rdx = L.dg) := by
  have h208 := hc.inFr (d := 208) (by omega_arith) (by omega_arith)
  have h216 := hc.inFr (d := 216) (by omega_arith) (by omega_arith)
  have h224 := hc.inFr (d := 224) (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  cases wide
  · simp only [Cfg.msgPtrs, Bool.false_eq_true, ite_false, List.append_nil, fScratch, fD, runBlock_cons,
      runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk, hc.rsp, Offset.add_add, Nat.reduceAdd, h208,
      h224, ite_true, Option.map_some, hc.pScr, hc.pD, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      RegUpd.mem_setReg, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
    exact ⟨hc.regs hL rfl rfl rfl rfl (by cs_tac), by triv, by triv, by triv, fun h => absurd h (by decide)⟩
  · simp only [Cfg.msgPtrs, ite_true, List.cons_append, List.nil_append, fScratch, fD, fDigest, runBlock_cons,
      runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk, hc.rsp, Offset.add_add, Nat.reduceAdd, h208,
      h216, h224, ite_true, Option.map_some, hc.pScr, hc.pD, hc.pDg, RegUpd.gpr_setReg, RegUpd.rd_setReg,
      RegUpd.wr_setReg, RegUpd.mem_setReg, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
    exact ⟨hc.regs hL rfl rfl rfl rfl (by cs_tac), by triv, by triv, by triv, fun _ => by triv⟩

/-- `Q` bytes copied to `scratch + d` by `copyBytes`, with `Ctx` kept. -/
theorem copyB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : Addr} (hs : u.gpr src = S)
    (hsr : src ≠ .rax) (hdi : u.gpr .rdi = L.scr) {so d Q : Nat} (h8 : 8 ≤ Q) (hd : d + Q ≤ 8192)
    (hso : so + Q < 2 ^ 64)
    (hr : ∀ j, j + 8 ≤ Q → InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (so + j)) 8)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, Q⟩ ⟨L.scr + BitVec.ofNat 64 d, Q⟩) :
    WP isa (.block (Cfg.copyBytes Q src so .rdi d)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.scr + BitVec.ofNat 64 d, Q⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 d) Q =
        Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 so) Q :=
  WP.mono_syms (copyBytes_ok (by decide) hsr hsep h8 hso (by omega_arith) hs hdi hr fun j hj => hc.inScrW (by omega_arith))
    fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy =>
    ⟨hc.keep hL hrd hwr (hg _ (by decide)) (fun r hr _ => hg r (ne_cs hr (by decide))) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L hd) hsy, hg, hf, hb⟩

/-- `V ‖ b`, for `V` of `D` bytes, with `scratch` in `rdi`. -/
theorem head_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .rdi = L.scr) (b : Nat) {D : Nat}
    (hD : D ≤ 64) (hD8 : 8 ≤ D) :
    WP isa (.block (Cfg.copyBytes D .rsp fV .rdi sMsg ++
      ([.mov32 .rax (.imm (BitVec.ofNat 32 b)), .store8 (at_ .rdi (sMsg + D)) .rax] : List Instr))) t fun u =>
      Ctx L g m₀ u ∧ (∀ r, r ≠ .rax → u.gpr r = t.gpr r) ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, D + 1⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) (D + 1) =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 88) D ++ [BitVec.ofNat 8 b] := by
  simp only [fV, sMsg]
  rw [WP.block_append_iff]
  refine WP.mono (copyB_ok hL hc (S := L.B + BitVec.ofNat 64 24) (src := .rsp) hc.rsp (by decide) hdi
    (so := 64) (d := 2256) (Q := D) hD8 (by omega_arith) (by omega_arith)
    (fun j hj => by rw [fr_add]; exact hc.inFr (by omega_arith) (by omega_arith))
    (by rw [fr_add]; exact hL.stk_scr (by omega_arith) (by omega_arith))) fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  have hdi₂ : u₂.gpr .rdi = L.scr := (hg₂ _ (by decide)).trans hdi
  have w := hc₂.inScrW (o := 2256 + D) (n := 1) (by omega_arith)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, State.store8, ea_at,
    RegUpd.gpr_setReg, reduceCtorEq, ite_false, RegUpd.mem_setReg, hdi₂,
    RegUpd.wr_setReg, w, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  have hb8 : ((BitVec.ofNat 32 b).setWidth 64).setWidth 8 = BitVec.ofNat 8 b := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [hb8]
  have hf₃ : Frame [⟨L.scr + BitVec.ofNat 64 (2256 + D), 1⟩] u₂.mem
      (u₂.mem.writeW (L.scr + BitVec.ofNat 64 (2256 + D)) (BitVec.ofNat 8 b)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc₂.keep hL rfl rfl (by trivial)
      (fun r hr hr' => by first | trivial | rfl | exact RegUpd.gpr_setReg_of_ne _ _ (ne_cs hr (by decide))) hf₃
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega_arith)) rfl,
    fun r hr => ?_, ?_, ?_⟩
  · simp only [hr, ite_false]; exact hg₂ r hr
  · refine (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_arith) (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_arith) (by omega_arith)
  · rw [Proof.Hmac.Common.bytesAt_add, Offset.add_add]
    have e₁ : Spec.Sha256.bytesAt (u₂.mem.writeW (L.scr + BitVec.ofNat 64 (2256 + D)) (BitVec.ofNat 8 b))
        (L.scr + BitVec.ofNat 64 2256) D = Spec.Sha256.bytesAt u₂.mem (L.scr + BitVec.ofNat 64 2256) D :=
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)
    rw [e₁, hb₂, fr_add]
    refine congrArg (fun y => Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (24 + 64)) D ++ y) ?_
    show [(u₂.mem.writeW (L.scr + BitVec.ofNat 64 (2256 + D)) (BitVec.ofNat 8 b))
      (L.scr + BitVec.ofNat 64 (2256 + D) + BitVec.ofNat 64 0)] = _
    rw [add_ofNat_zero, WriteBytes.writeW8_apply]; simp

/-- `‖ d ‖ h`, `Q` bytes each, after `D + 1` bytes, with `scratch` in `rdi`
and `d` in `rsi`. -/
theorem tail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hdi : u.gpr .rdi = L.scr) (hsi : u.gpr .rsi = L.d)
    {D Q : Nat} (hD : D ≤ 64) (h8 : 8 ≤ Q) (hQ : Q ≤ 48) (hq : Q ≤ L.q) :
    WP isa (.block (Cfg.copyBytes Q .rsi 0 .rdi (2256 + D + 1) ++ Cfg.copyBytes Q .rsp fH .rdi (2256 + D + 1 + Q))) u
      fun u' => Ctx L g m₀ u' ∧ Frame [⟨L.scr + BitVec.ofNat 64 (2256 + D + 1), 2 * Q⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 (2256 + D + 1)) (2 * Q) =
          Spec.Sha256.bytesAt u.mem L.d Q ++
            Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 152) Q := by
  simp only [fH]
  rw [WP.block_append_iff]
  refine WP.mono (copyB_ok hL hc (src := .rsi) hsi (by decide) hdi (so := 0) (d := 2256 + D + 1) h8 (by omega_arith)
    (by omega_arith) (fun j hj => by rw [Nat.zero_add]; exact hc.inD (by omega_arith) (by omega_arith))
    (by rw [add_ofNat_zero]
        exact (hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by omega_arith))))
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  have hdi₂ : u₂.gpr .rdi = L.scr := (hg₂ _ (by decide)).trans hdi
  refine WP.mono (copyB_ok hL hc₂ (S := L.B + BitVec.ofNat 64 24) (src := .rsp) hc₂.rsp (by decide) hdi₂
    (so := 128) (d := 2256 + D + 1 + Q) h8 (by omega_arith) (by omega_arith)
    (fun j hj => by rw [fr_add]; exact hc₂.inFr (by omega_arith) (by omega_arith))
    (by rw [fr_add]; exact hL.stk_scr (by omega_arith) (by omega_arith))) fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ?_
  refine ⟨hc₃, ?_, ?_⟩
  · refine (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_arith) (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_arith) (by omega_arith)
  · rw [show 2 * Q = Q + Q by omega_arith, Proof.Hmac.Common.bytesAt_add _ _ Q Q, Offset.add_add,
      hb₃, fr_add,
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith), hb₂, add_ofNat_zero]
    refine congrArg (fun y => Spec.Sha256.bytesAt u.mem L.d Q ++ y) ?_
    exact bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by omega_arith) (by omega_arith)) (by omega_arith)

/-- A zero word at `scratch + o`, with `scratch` in `rdi`. -/
theorem zeroW_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hdi : u.gpr .rdi = L.scr) {o : Nat}
    (ho : o + 8 ≤ 8192) :
    WP isa (.block [.alu32 .xor .rax (.reg .rax), .store (at_ .rdi o) .rax]) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.scr + BitVec.ofNat 64 o, 8⟩] u.mem u'.mem ∧
      ∀ k ≤ 8, Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 o) k = List.replicate k 0 := by
  have w := hc.inScrW (o := o) (n := 8) ho
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, State.setReg32,
    State.store64, ea_at, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_false, ite_true, hdi,
    RegUpd.wr_setReg, RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags, w, Option.bind_some,
    Option.some.injEq, exists_eq_left', xor_self_zx]
  have hf : Frame [⟨L.scr + BitVec.ofNat 64 o, 8⟩] u.mem (u.mem.writeW (L.scr + BitVec.ofNat 64 o) (0 : BitVec 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep hL rfl rfl (by triv) (fun r hr _ => ?_) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L ho) rfl,
    fun r hr => ?_, hf, fun k hk => ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ne_cs hr (by decide : Reg.rax ∉ calleeSaved), ite_false]
  · simp only [hr, ite_false]
  · rw [bytesAt_take _ _ (k := 8 * 1) (by omega_arith), bytesAt_of_readW (k := 1) _ _ 0 fun j hj => by
      rw [show j = 0 by omega_arith, Nat.mul_zero, add_ofNat_zero, Mem.readW_writeW_self64],
      show (List.range (8 * 1)).map (fun i => (0 : BitVec 64).extractLsb' (8 * (i % 8)) 8) =
        List.replicate 8 0 by decide, List.take_replicate, Nat.min_eq_left hk]

/-- `‖ d ‖ h` for two `V`s to a candidate, `Q` bytes each, after `D + 1` bytes,
with `scratch` in `rdi`, `d` in `rsi` and `digest` in `rdx`: `h` is `Q - D`
zero bytes then the digest. -/
theorem tailW_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hdi : u.gpr .rdi = L.scr)
    (hsi : u.gpr .rsi = L.d) (hdx : u.gpr .rdx = L.dg) {D Q : Nat} (hD : D ≤ 64) (hD8 : D % 8 = 0) (h8 : 8 ≤ Q)
    (hQD : D ≤ Q) (hQD8 : Q ≤ D + 8) (hq : Q ≤ L.q) (hdn : D ≤ dn) :
    WP isa (.block (Cfg.copyBytes Q .rsi 0 .rdi (2256 + D + 1) ++
      ([.alu32 .xor .rax (.reg .rax), .store (at_ .rdi (2256 + D + 1 + Q)) .rax] : List Instr) ++
      Cfg.copyN (D / 8) .rdx 0 .rdi (2256 + 1 + 2 * Q))) u
      fun u' => Ctx L g m₀ u' ∧ Frame [⟨L.scr + BitVec.ofNat 64 (2256 + D + 1), 2 * Q⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 (2256 + D + 1)) (2 * Q) =
          Spec.Sha256.bytesAt u.mem L.d Q ++ (List.replicate (Q - D) 0 ++ Spec.Sha256.bytesAt u.mem L.dg D) := by
  have e8 : 8 * (D / 8) = D := by omega_arith
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copyB_ok hL hc (src := .rsi) hsi (by decide) hdi (so := 0) (d := 2256 + D + 1) h8 (by omega_arith)
    (by omega_arith) (fun j hj => by rw [Nat.zero_add]; exact hc.inD (by omega_arith) (by omega_arith))
    (by rw [add_ofNat_zero]
        exact (hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by omega_arith))))
    fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
  have hdi₁ : u₁.gpr .rdi = L.scr := (hg₁ _ (by decide)).trans hdi
  have hdx₁ : u₁.gpr .rdx = L.dg := (hg₁ _ (by decide)).trans hdx
  refine WP.mono (zeroW_ok hL hc₁ hdi₁ (o := 2256 + D + 1 + Q) (by omega_arith)) fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  have hdi₂ : u₂.gpr .rdi = L.scr := (hg₂ _ (by decide)).trans hdi₁
  have hdx₂ : u₂.gpr .rdx = L.dg := (hg₂ _ (by decide)).trans hdx₁
  refine WP.mono (copy_ok hL hc₂ (S := L.dg) (src := .rdx) hdx₂ (by decide) hdi₂ (so := 0)
    (d := 2256 + 1 + 2 * Q) (K := D / 8) (by omega_arith)
    (fun j hj => by rw [Nat.zero_add]; exact hc₂.inDg (by omega_arith) (by omega_arith))
    (by rw [add_ofNat_zero, e8]
        exact (hL.gc.sub_left (Region.sub_prefix hdn)).sub_right (Offset.sub_base _ (by omega_arith))))
    fun u₃ ⟨hc₃, _, _, _, hf₃, hb₃⟩ => ?_
  rw [e8] at hf₃ hb₃
  refine ⟨hc₃, ?_, ?_⟩
  · refine ((hf₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    all_goals simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)
  · -- The private key, then the zero bytes and the digest.
    have hg₁' : Spec.Sha256.bytesAt u₁.mem L.dg D = Spec.Sha256.bytesAt u.mem L.dg D :=
      bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hL.gc.sub_left (Region.sub_prefix hdn)).sub_right (Offset.sub_base _ (by omega_arith))) (by omega_arith)
    have hg₂' : Spec.Sha256.bytesAt u₂.mem L.dg D = Spec.Sha256.bytesAt u₁.mem L.dg D :=
      bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hL.gc.sub_left (Region.sub_prefix hdn)).sub_right (Offset.sub_base _ (by omega_arith))) (by omega_arith)
    rw [show 2 * Q = Q + ((Q - D) + D) by omega_arith, Proof.Hmac.Common.bytesAt_add,
      Proof.Hmac.Common.bytesAt_add _ _ (Q - D) D, Offset.add_add, Offset.add_add,
      show 2256 + D + 1 + Q + (Q - D) = 2256 + 1 + 2 * Q by omega_arith, hb₃, add_ofNat_zero, hg₂', hg₁']
    congr 1
    · rw [bytesAt_frame hf₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith),
        bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith), hb₁, add_ofNat_zero]
    · refine congrArg (· ++ Spec.Sha256.bytesAt u.mem L.dg D) ?_
      rw [bytesAt_frame hf₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)]
      exact hb₂ _ (by omega_arith)

/-- `h` in the message: from the frame (`Q` bytes), or, if `wide`, `Q - D`
zero bytes then the digest. -/
abbrev hPart (wide : Bool) (Q D : Nat) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  if wide then List.replicate (Q - D) 0 ++ Spec.Sha256.bytesAt m L.dg D
  else Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 152) Q

/-- The message `V ‖ b` (`‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + 2256`, for `V` of `D` bytes. -/
theorem msg_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .rdi = L.scr) (hsi : t.gpr .rsi = L.d)
    (b : Nat) (full wide : Bool) (hdx : wide = true → t.gpr .rdx = L.dg) {D Q : Nat} (hD : D ≤ 64)
    (hD8 : 8 ≤ D) (h8 : 8 ≤ Q) (hQ : Q ≤ 72) (hq : Q ≤ L.q)
    (hA : full = true → wide = false → Q ≤ 48)
    (hW : full = true → wide = true → D ≤ Q ∧ Q ≤ D + 8 ∧ D ≤ dn ∧ D % 8 = 0) :
    WP isa (.block (Cfg.msg Q D b full wide)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, D + 2 * Q + 1⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.scr + BitVec.ofNat 64 2256) (if full then D + 2 * Q + 1 else D + 1) =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 88) D ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem L.d Q ++ hPart wide Q D L t.mem else []) := by
  cases full
  · simp only [Cfg.msg, Bool.false_eq_true, ite_false, List.append_nil]
    refine WP.mono (head_ok hL hc hdi b hD hD8) fun u ⟨hcu, _, hf, hb⟩ =>
      ⟨hcu, hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩, hb⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub _ (by omega_arith) (by omega_arith)
  · simp only [Cfg.msg, ite_true, sMsg]
    rw [WP.block_append_iff]
    refine WP.mono (head_ok hL hc hdi b hD hD8) fun u ⟨hcu, hg, hf, hb⟩ => ?_
    have hdi' : u.gpr .rdi = L.scr := (hg _ (by decide)).trans hdi
    have hsi' : u.gpr .rsi = L.d := (hg _ (by decide)).trans hsi
    -- The tail, and what it is made of, unchanged by the head.
    suffices h : WP isa (.block (if wide then
          Cfg.copyBytes Q .rsi 0 .rdi (2256 + D + 1) ++
            ([.alu32 .xor .rax (.reg .rax), .store (at_ .rdi (2256 + D + 1 + Q)) .rax] : List Instr) ++
            Cfg.copyN (D / 8) .rdx 0 .rdi (2256 + 1 + 2 * Q)
        else Cfg.copyBytes Q .rsi 0 .rdi (2256 + D + 1) ++ Cfg.copyBytes Q .rsp fH .rdi (2256 + D + 1 + Q))) u
        fun u' => Ctx L g m₀ u' ∧ Frame [⟨L.scr + BitVec.ofNat 64 (2256 + D + 1), 2 * Q⟩] u.mem u'.mem ∧
          Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 (2256 + D + 1)) (2 * Q) =
            Spec.Sha256.bytesAt u.mem L.d Q ++ hPart wide Q D L u.mem by
      refine WP.mono h fun u' ⟨hcu', hf', hb'⟩ => ⟨hcu', ?_, ?_⟩
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
        refine congrArg (fun y => Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 88) D ++ [BitVec.ofNat 8 b] ++ y) ?_
        have hdq : Spec.Sha256.bytesAt u.mem L.d Q = Spec.Sha256.bytesAt t.mem L.d Q :=
          bytesAt_frame hf (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by omega_arith))) (by omega_arith)
        rw [hdq]
        refine congrArg (Spec.Sha256.bytesAt t.mem L.d Q ++ ·) ?_
        cases wide
        · simp only [hPart, Bool.false_eq_true, ite_false]
          exact bytesAt_frame hf (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact hL.stk_scr (by omega_arith) (by omega_arith)) (by omega_arith)
        · obtain ⟨_, _, hdn, -⟩ := hW rfl rfl
          simp only [hPart, ite_true]
          refine congrArg (List.replicate (Q - D) 0 ++ ·) ?_
          exact bytesAt_frame hf (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (hL.gc.sub_left (Region.sub_prefix hdn)).sub_right (Offset.sub_base _ (by omega_arith))) (by omega_arith)
    cases wide
    · have hQ48 := hA rfl rfl
      simp only [Bool.false_eq_true, ite_false, hPart]
      exact tail_ok hL hcu hdi' hsi' hD h8 hQ48 hq
    · obtain ⟨hQD, hQD8, hdn, hD8'⟩ := hW rfl rfl
      simp only [ite_true, hPart]
      exact tailW_ok hL hcu hdi' hsi' ((hg _ (by decide)).trans (hdx rfl)) hD hD8' h8 hQD hQD8 hq hdn

end VG.Proof.Ecdsa.Rfc6979.X86_64
