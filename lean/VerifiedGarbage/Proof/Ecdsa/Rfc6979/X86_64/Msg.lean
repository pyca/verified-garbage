module
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86_64
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Layout
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Hash

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-!
# Deterministic ECDSA on x86-64: the messages of steps d, f and h.3

The byte `b`, and `‖ d ‖ h` if `full`, at `scratch + 2256` (`msg_ok`): the
byte (`byte_ok`), then the private key and `h` copied (`tail_ok`). HMAC's
text is `V` (`D` bytes, from the frame, the table's `update` with it), then
this message.
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

/-- The pointers: `scratch` in `rdi` and `d` in `rsi`. -/
theorem ptrs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.msgPtrs) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .rdi = L.scr ∧
      u.gpr .rsi = L.d := by
  have h208 := hc.inFr (d := 208) (by omega_using []) (by omega_using [])
  have h224 := hc.inFr (d := 224) (by omega_using []) (by omega_using [])
  apply WP.of_runBlock
  simp only [Cfg.msgPtrs, fScratch, fD, runBlock_cons,
    runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk, hc.rsp, Offset.add_add, Nat.reduceAdd, h208,
    h224, ite_true, Option.map_some, hc.pScr, hc.pD, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs hL rfl rfl rfl rfl (by cs_tac), by triv, by triv, by triv⟩

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
  WP.mono_syms (copyBytes_ok (by decide) hsr hsep h8 hso (by omega_using [hd]) hs hdi hr fun j hj => hc.inScrW (by omega_using [hd, hj]))
    fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy =>
    ⟨hc.keep hL hrd hwr (hg _ (by decide)) (fun r hr _ => hg r (ne_cs hr (by decide))) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L hd) hsy, hg, hf, hb⟩

/-- The byte `b` at `scratch + 2256`, with `scratch` in `rdi`. -/
theorem byte_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .rdi = L.scr) (b : Nat) :
    WP isa (.block ([.mov32 .rax (.imm (BitVec.ofNat 32 b)), .store8 (at_ .rdi sMsg) .rax] : List Instr)) t
      fun u => Ctx L g m₀ u ∧ (∀ r, r ≠ .rax → u.gpr r = t.gpr r) ∧
        Frame [⟨L.scr + BitVec.ofNat 64 2256, 1⟩] t.mem u.mem ∧
        Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) 1 = [BitVec.ofNat 8 b] := by
  have w := hc.inScrW (o := 2256) (n := 1) (by decide)
  apply WP.of_runBlock
  simp only [sMsg, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, State.store8, ea_at,
    RegUpd.gpr_setReg, reduceCtorEq, ite_false, RegUpd.mem_setReg, hdi,
    RegUpd.wr_setReg, w, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  have hb8 : ((BitVec.ofNat 32 b).setWidth 64).setWidth 8 = BitVec.ofNat 8 b := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [hb8]
  have hf₃ : Frame [⟨L.scr + BitVec.ofNat 64 2256, 1⟩] t.mem
      (t.mem.writeW (L.scr + BitVec.ofNat 64 2256) (BitVec.ofNat 8 b)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep hL rfl rfl (by trivial)
      (fun r hr hr' => by first | trivial | rfl | exact RegUpd.gpr_setReg_of_ne _ _ (ne_cs hr (by decide))) hf₃
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by decide)) rfl,
    fun r hr => ?_, hf₃, ?_⟩
  · simp only [hr, ite_false]
  · show [(t.mem.writeW (L.scr + BitVec.ofNat 64 2256) (BitVec.ofNat 8 b))
      (L.scr + BitVec.ofNat 64 2256 + BitVec.ofNat 64 0)] = _
    rw [add_ofNat_zero, WriteBytes.writeW8_apply]; simp

/-- `d ‖ h`, `Q` bytes each, at `scratch + a`, with `scratch` in `rdi` and
`d` in `rsi`, `h` at `ho` in the frame. -/
theorem tail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hdi : u.gpr .rdi = L.scr) (hsi : u.gpr .rsi = L.d)
    {a Q ho : Nat} (ha : a + 2 * Q ≤ 8192) (h8 : 8 ≤ Q) (hQ : Q ≤ 66) (hho : 24 + ho + Q ≤ 240 + 8 * L.e)
    (hq : Q ≤ L.q) :
    WP isa (.block (Cfg.copyBytes Q .rsi 0 .rdi a ++ Cfg.copyBytes Q .rsp ho .rdi (a + Q))) u
      fun u' => Ctx L g m₀ u' ∧ Frame [⟨L.scr + BitVec.ofNat 64 a, 2 * Q⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 a) (2 * Q) =
          Spec.Sha256.bytesAt u.mem L.d Q ++
            Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + ho)) Q := by
  rw [WP.block_append_iff]
  refine WP.mono (copyB_ok hL hc (src := .rsi) hsi (by decide) hdi (so := 0) (d := a) h8 (by omega_using [ha])
    (by omega_using [hQ]) (fun j hj => by rw [Nat.zero_add]; exact hc.inD (by omega_using [hq, hj]) (by omega_using [hQ, hj]))
    (by rw [add_ofNat_zero]
        exact (hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by omega_using [ha]))))
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  have hdi₂ : u₂.gpr .rdi = L.scr := (hg₂ _ (by decide)).trans hdi
  refine WP.mono (copyB_ok hL hc₂ (S := L.B + BitVec.ofNat 64 24) (src := .rsp) hc₂.rsp (by decide) hdi₂
    (so := ho) (d := a + Q) h8 (by omega_using [ha]) (by have := L.he; omega_using [hho, this])
    (fun j hj => by rw [fr_add]; exact hc₂.inFr (by omega_using []) (by omega_using [hho, hj]))
    (by rw [fr_add]; exact hL.stk_scr (by omega_using [hho]) (by omega_using [ha]))) fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ?_
  refine ⟨hc₃, ?_, ?_⟩
  · refine (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_using []) (by omega_using [])
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_using []) (by omega_using [])
  · rw [show 2 * Q = Q + Q by omega_using [], Proof.Hmac.Common.bytesAt_add _ _ Q Q, Offset.add_add,
      hb₃, fr_add,
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_using []) (by omega_using [ha]) (by omega_using [ha])) (by omega_using [hQ]),
      hb₂, add_ofNat_zero]
    refine congrArg (fun y => Spec.Sha256.bytesAt u.mem L.d Q ++ y) ?_
    exact bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by omega_using [hho]) (by omega_using [ha])) (by omega_using [hQ])

variable {P : RfcHash}

/-- `h` in the frame. -/
abbrev hOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 (24 + (cfgOf P).fHo)) P.Q

/-- The length of the message. -/
abbrev mlen (P : RfcHash) (full : Bool) : Nat := if full then 1 + 2 * P.Q else 1

/-- The message `b` (`‖ d ‖ h` if `full`, `Q` bytes each) at `scratch + 2256`. -/
theorem msg_ok (hL : L.Ok) (hq : L.q = P.Q) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .rdi = L.scr)
    (hsi : t.gpr .rsi = L.d) (b : Nat) (full : Bool) :
    WP isa (.block ((cfgOf P).msg b full)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, 1 + 2 * P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.scr + BitVec.ofNat 64 2256) (mlen P full) =
        [BitVec.ofNat 8 b] ++ (if full then Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem else []) := by
  have hQ := P.sizes
  have hlen : (cfgOf P).len = P.Q := rfl
  have hho : 24 + (cfgOf P).fHo + P.Q ≤ 240 + 8 * L.e := by
    have := L.he
    simp only [Cfg.fHo, cfgOf]
    rcases Bool.eq_false_or_eq_true P.R.big with h | h <;>
      simp only [h, fX, fH, ite_true, ite_false, Bool.false_eq_true] <;> nums
  cases full
  · simp only [Cfg.msg, Bool.false_eq_true, ite_false, List.append_nil, mlen]
    refine WP.mono (byte_ok hL hc hdi b) fun u ⟨hcu, _, hf, hb⟩ =>
      ⟨hcu, hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩, hb⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub _ (by omega_using []) (by omega_using [])
  · simp only [Cfg.msg, ite_true, sMsg, mlen]
    rw [WP.block_append_iff]
    refine WP.mono (byte_ok hL hc hdi b) fun u ⟨hcu, hg, hf, hb⟩ => ?_
    have hdi' : u.gpr .rdi = L.scr := (hg _ (by decide)).trans hdi
    have hsi' : u.gpr .rsi = L.d := (hg _ (by decide)).trans hsi
    refine WP.mono (tail_ok hL hcu hdi' hsi' (a := 2256 + 1) (Q := (cfgOf P).len) (ho := (cfgOf P).fHo)
      (by show _ + 2 * P.Q ≤ _; nums) (by show 8 ≤ P.Q; nums) (by show P.Q ≤ 66; nums) hho (by rw [hq]; rfl))
      fun u' ⟨hcu', hf', hb'⟩ => ⟨hcu', ?_, ?_⟩
    · refine (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub _ (by omega_using []) (by omega_using [])
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub _ (by omega_using []) (by omega_using [hlen])
    · rw [Proof.Hmac.Common.bytesAt_add _ _ 1 (2 * P.Q), Offset.add_add]
      have hb'' : Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 (2256 + 1)) (2 * P.Q) =
          Spec.Sha256.bytesAt u.mem L.d P.Q ++ hOf P L u.mem := hb'
      rw [hb'', bytesAt_frame hf' (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega_using []) (by omega_using []) (by nums)) (by omega_using []), hb]
      refine congrArg ([BitVec.ofNat 8 b] ++ ·) ?_
      have hdq : Spec.Sha256.bytesAt u.mem L.d P.Q = Spec.Sha256.bytesAt t.mem L.d P.Q :=
        bytesAt_frame hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hL.dc.sub_left (Region.sub_prefix (by rw [hq]))).sub_right (Offset.sub_base _ (by omega_using [])))
          (by nums)
      rw [hdq]
      refine congrArg (Spec.Sha256.bytesAt t.mem L.d P.Q ++ ·) ?_
      exact bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hL.stk_scr (by omega_using [hho]) (by omega_using [])) (by nums)

end VG.Proof.Ecdsa.Rfc6979.X86_64
