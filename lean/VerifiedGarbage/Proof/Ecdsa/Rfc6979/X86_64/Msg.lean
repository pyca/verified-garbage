module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Blocks
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce
import VerifiedGarbage.Proof.Mont.X86_64.Row
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy

/-!
# Deterministic ECDSA on x86-64: the messages of steps d, f and h.3

`V ‖ b`, and `‖ d ‖ h` if `full`, at `scratch + 2256`, for `V` of `D` bytes
(`msg_ok`): `V` copied from the frame (`head_ok`), the byte `b`, then the
private key and `h` copied (`tail_ok`), or, if `wide`, the private key, a
zero word and the digest, which leaves `h` as `Q - D` zero bytes then the
digest (`tailW_ok`).
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
  WP.mono_sf (copyN_ok (K := K) (by decide) hsr hsep (by have := hL.nc; omega_using [hd]) K (Nat.le_refl _) u hs hdi hr
    fun j hj => hc.inScrW (by omega_using [hd, hj])) fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy =>
    ⟨hc.keep hL hrd hwr (hg _ (by decide)) (fun r hr _ => hg r (ne_cs hr (by decide))) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L hd) hsy,
      hrd, hwr, hg, hf, hb⟩

theorem fr_add (B : Addr) (o : Nat) : B + BitVec.ofNat 64 24 + BitVec.ofNat 64 o = B + BitVec.ofNat 64 (24 + o) :=
  Offset.add_add _ _ _

/-- The pointers: `scratch` in `rdi`, `d` in `rsi`, and, if `wide`, `digest` in `rdx`. -/
theorem ptrs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (wide : Bool) :
    WP isa (.block (Cfg.msgPtrs wide)) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .rdi = L.scr ∧
      u.gpr .rsi = L.d ∧ (wide = true → u.gpr .rdx = L.dg) := by
  have h208 := hc.inFr (d := 208) (by omega_using []) (by omega_using [])
  have h216 := hc.inFr (d := 216) (by omega_using []) (by omega_using [])
  have h224 := hc.inFr (d := 224) (by omega_using []) (by omega_using [])
  apply WP.of_runBlock
  cases wide
  · simp only [Cfg.msgPtrs, Bool.false_eq_true, ite_false, List.append_nil, fScratch, fD, runBlock_cons,
      runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk, hc.rsp, Offset.add_add, Nat.reduceAdd, h208,
      h224, ite_true, Option.map_some, hc.pScr, hc.pD, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      RegUpd.mem_setReg, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
    exact ⟨hc.regs hL rfl rfl rfl ⟨rfl, rfl⟩ (by cs_tac), by triv, by triv, by triv, fun h => absurd h (by decide)⟩
  · simp only [Cfg.msgPtrs, ite_true, List.cons_append, List.nil_append, fScratch, fD, fDigest, runBlock_cons,
      runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk, hc.rsp, Offset.add_add, Nat.reduceAdd, h208,
      h216, h224, ite_true, Option.map_some, hc.pScr, hc.pD, hc.pDg, RegUpd.gpr_setReg, RegUpd.rd_setReg,
      RegUpd.wr_setReg, RegUpd.mem_setReg, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
    exact ⟨hc.regs hL rfl rfl rfl ⟨rfl, rfl⟩ (by cs_tac), by triv, by triv, by triv, fun _ => by triv⟩

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
  WP.mono_sf (copyBytes_ok (by decide) hsr hsep h8 hso (by omega_using [hd]) hs hdi hr fun j hj => hc.inScrW (by omega_using [hd, hj]))
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
    (so := 64) (d := 2256) (Q := D) hD8 (by omega_using [hD]) (by omega_using [hD])
    (fun j hj => by rw [fr_add]; exact hc.inFr (by omega_using []) (by omega_using [hD, hj]))
    (by rw [fr_add]; exact hL.stk_scr (by omega_using [hD]) (by omega_using [hD]))) fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  have hdi₂ : u₂.gpr .rdi = L.scr := (hg₂ _ (by decide)).trans hdi
  have w := hc₂.inScrW (o := 2256 + D) (n := 1) (by omega_using [hD])
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
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega_using [hD])) ⟨rfl, rfl⟩,
    fun r hr => ?_, ?_, ?_⟩
  · simp only [hr, ite_false]; exact hg₂ r hr
  · refine (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_using []) (by omega_using [])
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_using []) (by omega_using [])
  · rw [Proof.Hmac.Common.bytesAt_add, Offset.add_add]
    have e₁ : Spec.Sha256.bytesAt (u₂.mem.writeW (L.scr + BitVec.ofNat 64 (2256 + D)) (BitVec.ofNat 8 b))
        (L.scr + BitVec.ofNat 64 2256) D = Spec.Sha256.bytesAt u₂.mem (L.scr + BitVec.ofNat 64 2256) D :=
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_using []) (by omega_using [hD]) (by omega_using [hD])) (by omega_using [hD])
    rw [e₁, hb₂, fr_add]
    refine congrArg (fun y => Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (24 + 64)) D ++ y) ?_
    show [(u₂.mem.writeW (L.scr + BitVec.ofNat 64 (2256 + D)) (BitVec.ofNat 8 b))
      (L.scr + BitVec.ofNat 64 (2256 + D) + BitVec.ofNat 64 0)] = _
    rw [add_ofNat_zero, WriteBytes.writeW8_apply]; simp

/-- `‖ d ‖ h`, `Q` bytes each, after `D + 1` bytes, with `scratch` in `rdi`
and `d` in `rsi`, `h` at `ho` in the frame. -/
theorem tail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hdi : u.gpr .rdi = L.scr) (hsi : u.gpr .rsi = L.d)
    {D Q ho : Nat} (hD : D ≤ 64) (h8 : 8 ≤ Q) (hQ : Q ≤ 64) (hho : 24 + ho + Q ≤ 240 + 8 * L.e) (hq : Q ≤ L.q) :
    WP isa (.block (Cfg.copyBytes Q .rsi 0 .rdi (2256 + D + 1) ++ Cfg.copyBytes Q .rsp ho .rdi (2256 + D + 1 + Q))) u
      fun u' => Ctx L g m₀ u' ∧ Frame [⟨L.scr + BitVec.ofNat 64 (2256 + D + 1), 2 * Q⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 (2256 + D + 1)) (2 * Q) =
          Spec.Sha256.bytesAt u.mem L.d Q ++
            Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + ho)) Q := by
  rw [WP.block_append_iff]
  refine WP.mono (copyB_ok hL hc (src := .rsi) hsi (by decide) hdi (so := 0) (d := 2256 + D + 1) h8 (by omega_using [hD, hQ])
    (by omega_using [hQ]) (fun j hj => by rw [Nat.zero_add]; exact hc.inD (by omega_using [hq, hj]) (by omega_using [hQ, hj]))
    (by rw [add_ofNat_zero]
        exact (hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by omega_using [hD, hQ]))))
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  have hdi₂ : u₂.gpr .rdi = L.scr := (hg₂ _ (by decide)).trans hdi
  refine WP.mono (copyB_ok hL hc₂ (S := L.B + BitVec.ofNat 64 24) (src := .rsp) hc₂.rsp (by decide) hdi₂
    (so := ho) (d := 2256 + D + 1 + Q) h8 (by omega_using [hD, hQ]) (by have := L.he; omega_using [hho, this])
    (fun j hj => by rw [fr_add]; exact hc₂.inFr (by omega_using []) (by omega_using [hho, hj]))
    (by rw [fr_add]; exact hL.stk_scr (by omega_using [hho]) (by omega_using [hD, hQ]))) fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ?_
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
        exact Offset.disjoint _ (by omega_using []) (by omega_using [hD, hQ]) (by omega_using [hD, hQ])) (by omega_using [hQ]), hb₂, add_ofNat_zero]
    refine congrArg (fun y => Spec.Sha256.bytesAt u.mem L.d Q ++ y) ?_
    exact bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by omega_using [hho]) (by omega_using [hD, hQ])) (by omega_using [hQ])

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
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L ho) ⟨rfl, rfl⟩,
    fun r hr => ?_, hf, fun k hk => ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ne_cs hr (by decide : Reg.rax ∉ calleeSaved), ite_false]
  · simp only [hr, ite_false]
  · rw [bytesAt_take _ _ (k := 8 * 1) (by omega_using [hk]), bytesAt_of_readW (k := 1) _ _ 0 fun j hj => by
      rw [show j = 0 by omega_using [hj], Nat.mul_zero, add_ofNat_zero, Mem.readW_writeW_self64],
      show (List.range (8 * 1)).map (fun i => (0 : BitVec 64).extractLsb' (8 * (i % 8)) 8) =
        List.replicate 8 0 by decide, List.take_replicate, Nat.min_eq_left hk]

/-- The 8 bytes of a zero word. -/
theorem bytesAt_zero64 (m : Mem) (q : Addr) {n : Nat} (hn : n ≤ 8) :
    Spec.Sha256.bytesAt (m.writeW q (0 : BitVec 64)) q n = List.replicate n 0 := by
  rw [bytesAt_take _ _ (k := 8 * 1) (by omega_using [hn]), bytesAt_of_readW (k := 1) _ _ 0 fun j hj => by
    rw [show j = 0 by omega_using [hj], Nat.mul_zero, add_ofNat_zero, Mem.readW_writeW_self64],
    show (List.range (8 * 1)).map (fun i => (0 : BitVec 64).extractLsb' (8 * (i % 8)) 8) =
      List.replicate 8 0 by decide, List.take_replicate, Nat.min_eq_left hn]

/-- `k` zero words at `[dst + d]`, `rax` zero. -/
theorem zeroN_words {dst : Reg} {D : Addr} {d K : Nat} (hdr : dst ≠ .rax) (hdn : d + 8 * K < 2 ^ 64) :
    ∀ k ≤ K, ∀ u : State, u.gpr dst = D → u.gpr .rax = 0 →
      (∀ j < K, InRegions u.wr (D + BitVec.ofNat 64 (d + 8 * j)) 8) →
      WP isa (.block (Cfg.zeroN k dst d)) u fun u' =>
        u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.gpr = u.gpr ∧ Frame [⟨D + BitVec.ofNat 64 d, 8 * K⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (D + BitVec.ofNat 64 d) (8 * k) = List.replicate (8 * k) 0
  | 0, _, u, _, _, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, rfl, Frame.refl _ _, rfl⟩
  | k + 1, hk, u, hd, ha, hw => by
    rw [Cfg.zeroN, List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeroN_words hdr hdn k (by omega) u hd ha hw) fun u₁ ⟨hrd, hwr, hg, hf, hb⟩ => ?_
    have w := hw k (by omega)
    rw [← hwr] at w
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_at, hg, hd, ha, w, ite_true,
      Option.some.injEq, exists_eq_left']
    have hf₂ : Frame [⟨D + BitVec.ofNat 64 (d + 8 * k), 8⟩] u₁.mem
        (u₁.mem.writeW (D + BitVec.ofNat 64 (d + 8 * k)) (0 : BitVec 64)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    refine ⟨hrd, by triv, by triv, hf.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)⟩), ?_⟩
    rw [show 8 * (k + 1) = 8 * k + 8 by omega, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
      bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), hb, bytesAt_zero64 _ _ (Nat.le_refl _),
      List.replicate_append_replicate]

/-- `rax ← 0`. -/
theorem zeroRax_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) :
    WP isa (.block [.alu32 .xor .rax (.reg .rax)]) u (Upd L g m₀ u .rax 0) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, State.setReg32,
    Option.bind_some, Option.some.injEq, exists_eq_left', xor_self_zx]
  exact ⟨hc.set hL (d := .rax) (by decide) rfl rfl rfl ⟨rfl, rfl⟩ fun r hr => by
      rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags],
    rfl, RegUpd.gpr_setReg_self _ _ _, fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]⟩

/-- `‖ d ‖ h` for a hash shorter than the scalars, `Q` bytes each, after
`D + 1` bytes, with `scratch` in `rdi`, `d` in `rsi` and `digest` in `rdx`:
`h` is `Q - D` zero bytes (zero words, which the digest's words then
overwrite but for them) then the digest. -/
theorem tailW_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hdi : u.gpr .rdi = L.scr)
    (hsi : u.gpr .rsi = L.d) (hdx : u.gpr .rdx = L.dg) {D Q : Nat} (hD : D ≤ 64) (hD8 : 8 ≤ D)
    (hQD : D < Q) (hQ : Q ≤ 66) (hq : Q ≤ L.q) (hdn : D ≤ dn) :
    WP isa (.block (Cfg.copyBytes Q .rsi 0 .rdi (2256 + D + 1) ++ ([.alu32 .xor .rax (.reg .rax)] : List Instr) ++
      Cfg.zeroN ((Q - D + 7) / 8) .rdi (2256 + D + 1 + Q) ++ Cfg.copyBytes D .rdx 0 .rdi (2256 + 1 + 2 * Q))) u
      fun u' => Ctx L g m₀ u' ∧ Frame [⟨L.scr + BitVec.ofNat 64 (2256 + D + 1), 2 * Q⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 (2256 + D + 1)) (2 * Q) =
          Spec.Sha256.bytesAt u.mem L.d Q ++ (List.replicate (Q - D) 0 ++ Spec.Sha256.bytesAt u.mem L.dg D) := by
  have hK : 8 * ((Q - D + 7) / 8) ≤ Q - D + 7 := by omega
  have hK' : Q - D ≤ 8 * ((Q - D + 7) / 8) := by omega
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copyB_ok hL hc (src := .rsi) hsi (by decide) hdi (so := 0) (d := 2256 + D + 1) (by omega)
    (by omega) (by omega) (fun j hj => by rw [Nat.zero_add]; exact hc.inD (by omega) (by omega))
    (by rw [add_ofNat_zero]
        exact (hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by omega))))
    fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
  refine WP.mono (zeroRax_ok hL hc₁) fun u₂ h₂ => ?_
  have hdi₂ : u₂.gpr .rdi = L.scr := (h₂.keep _ (by decide)).trans ((hg₁ _ (by decide)).trans hdi)
  have hdx₂ : u₂.gpr .rdx = L.dg := (h₂.keep _ (by decide)).trans ((hg₁ _ (by decide)).trans hdx)
  refine WP.mono_sf (zeroN_words (D := L.scr) (d := 2256 + D + 1 + Q) (K := (Q - D + 7) / 8) (by decide)
    (by omega) _ (Nat.le_refl _) u₂ hdi₂ h₂.val fun j hj => h₂.ctx.inScrW (by omega))
    fun u₃ ⟨hrd₃, hwr₃, hg₃, hf₃, hb₃⟩ hsy₃ => ?_
  have hc₃ : Ctx L g m₀ u₃ := h₂.ctx.keep hL hrd₃ hwr₃ (by rw [hg₃]) (fun r _ _ => by rw [hg₃]) hf₃
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega)) hsy₃
  have hdx₃ : u₃.gpr .rdx = L.dg := by rw [hg₃]; exact hdx₂
  have hdi₃ : u₃.gpr .rdi = L.scr := by rw [hg₃]; exact hdi₂
  refine WP.mono (copyB_ok hL hc₃ (S := L.dg) (src := .rdx) hdx₃ (by decide) hdi₃
    (so := 0) (d := 2256 + 1 + 2 * Q) (Q := D) hD8 (by omega) (by omega)
    (fun j hj => by rw [Nat.zero_add]; exact hc₃.inDg (by omega) (by omega))
    (by rw [add_ofNat_zero]
        exact (hL.gc.sub_left (Region.sub_prefix hdn)).sub_right (Offset.sub_base _ (by omega))))
    fun u₄ ⟨hc₄, _, hf₄, hb₄⟩ => ?_
  refine ⟨hc₄, ?_, ?_⟩
  · refine ((hf₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      ((h₂.mem ▸ hf₃).sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).trans
      (hf₄.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    all_goals simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)
  · -- The digest, unchanged by the private key's copy and the zero words.
    have hdg : ∀ {ws : List Region} {m m' : Mem}, Frame ws m m' →
        (∀ r ∈ ws, ∃ a n, r = ⟨L.scr + BitVec.ofNat 64 a, n⟩ ∧ a + n ≤ 8192) →
        Spec.Sha256.bytesAt m' L.dg D = Spec.Sha256.bytesAt m L.dg D := fun hf hws =>
      bytesAt_frame hf (fun r hr => by
        obtain ⟨a, n, rfl, h⟩ := hws r hr
        exact (hL.gc.sub_left (Region.sub_prefix hdn)).sub_right (Offset.sub_base _ h)) (by omega)
    have e₁ := hdg hf₁ fun r hr => ⟨2256 + D + 1, Q, by simpa using hr, by omega⟩
    have e₃ := hdg hf₃ fun r hr => ⟨2256 + D + 1 + Q, 8 * ((Q - D + 7) / 8), by simpa using hr, by omega⟩
    rw [show 2 * Q = Q + ((Q - D) + D) by omega, Proof.Hmac.Common.bytesAt_add,
      Proof.Hmac.Common.bytesAt_add _ _ (Q - D) D, Offset.add_add, Offset.add_add,
      show 2256 + D + 1 + Q + (Q - D) = 2256 + 1 + 2 * Q by omega, hb₄, add_ofNat_zero, e₃, h₂.mem, e₁]
    congr 1
    · rw [bytesAt_frame hf₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega),
        bytesAt_frame hf₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), h₂.mem, hb₁, add_ofNat_zero]
    · refine congrArg (· ++ Spec.Sha256.bytesAt u.mem L.dg D) ?_
      rw [bytesAt_frame hf₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega),
        bytesAt_take _ _ hK', hb₃, List.take_replicate, Nat.min_eq_left hK']

/-- `h` in the message: from the stack at `hb` (`Q` bytes), or, if `wide`,
`Q - D` zero bytes then the digest. -/
abbrev hPart (wide : Bool) (Q D hb : Nat) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  if wide then List.replicate (Q - D) 0 ++ Spec.Sha256.bytesAt m L.dg D
  else Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 hb) Q

/-- The message `V ‖ b` (`‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + 2256`, for `V` of `D` bytes. -/
theorem msg_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .rdi = L.scr) (hsi : t.gpr .rsi = L.d)
    (b : Nat) (full wide : Bool) (ho : Nat) (hdx : wide = true → t.gpr .rdx = L.dg) {D Q : Nat} (hD : D ≤ 64)
    (hD8 : 8 ≤ D) (h8 : 8 ≤ Q) (hQ : Q ≤ 72) (hq : Q ≤ L.q)
    (hA : full = true → wide = false → Q ≤ 64 ∧ 24 + ho + Q ≤ 240 + 8 * L.e)
    (hW : full = true → wide = true → D < Q ∧ Q ≤ 66 ∧ D ≤ dn) :
    WP isa (.block (Cfg.msg Q D b full wide ho)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, D + 2 * Q + 1⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.scr + BitVec.ofNat 64 2256) (if full then D + 2 * Q + 1 else D + 1) =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 88) D ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem L.d Q ++ hPart wide Q D (24 + ho) L t.mem else []) := by
  cases full
  · simp only [Cfg.msg, Bool.false_eq_true, ite_false, List.append_nil]
    refine WP.mono (head_ok hL hc hdi b hD hD8) fun u ⟨hcu, _, hf, hb⟩ =>
      ⟨hcu, hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩, hb⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub _ (by omega_using []) (by omega_using [])
  · simp only [Cfg.msg, ite_true, sMsg]
    rw [WP.block_append_iff]
    refine WP.mono (head_ok hL hc hdi b hD hD8) fun u ⟨hcu, hg, hf, hb⟩ => ?_
    have hdi' : u.gpr .rdi = L.scr := (hg _ (by decide)).trans hdi
    have hsi' : u.gpr .rsi = L.d := (hg _ (by decide)).trans hsi
    -- The tail, and what it is made of, unchanged by the head.
    suffices h : WP isa (.block (if wide then
          Cfg.copyBytes Q .rsi 0 .rdi (2256 + D + 1) ++ ([.alu32 .xor .rax (.reg .rax)] : List Instr) ++
            Cfg.zeroN ((Q - D + 7) / 8) .rdi (2256 + D + 1 + Q) ++ Cfg.copyBytes D .rdx 0 .rdi (2256 + 1 + 2 * Q)
        else Cfg.copyBytes Q .rsi 0 .rdi (2256 + D + 1) ++ Cfg.copyBytes Q .rsp ho .rdi (2256 + D + 1 + Q))) u
        fun u' => Ctx L g m₀ u' ∧ Frame [⟨L.scr + BitVec.ofNat 64 (2256 + D + 1), 2 * Q⟩] u.mem u'.mem ∧
          Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 (2256 + D + 1)) (2 * Q) =
            Spec.Sha256.bytesAt u.mem L.d Q ++ hPart wide Q D (24 + ho) L u.mem by
      refine WP.mono h fun u' ⟨hcu', hf', hb'⟩ => ⟨hcu', ?_, ?_⟩
      · refine (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
          (hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
        · simp only [List.mem_singleton] at hr; subst hr
          exact Offset.sub _ (by omega_using []) (by omega_using [])
        · simp only [List.mem_singleton] at hr; subst hr
          exact Offset.sub _ (by omega_using []) (by omega_using [])
      · rw [show D + 2 * Q + 1 = (D + 1) + 2 * Q by omega_using [], Proof.Hmac.Common.bytesAt_add _ _ (D + 1) (2 * Q),
          Offset.add_add, show 2256 + (D + 1) = 2256 + D + 1 by omega_using [], hb',
          bytesAt_frame hf' (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega_using []) (by omega_using [hD]) (by omega_using [hD, hQ])) (by omega_using [hD]), hb]
        refine congrArg (fun y => Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 88) D ++ [BitVec.ofNat 8 b] ++ y) ?_
        have hdq : Spec.Sha256.bytesAt u.mem L.d Q = Spec.Sha256.bytesAt t.mem L.d Q :=
          bytesAt_frame hf (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by omega_using [hD]))) (by omega_using [hQ])
        rw [hdq]
        refine congrArg (Spec.Sha256.bytesAt t.mem L.d Q ++ ·) ?_
        cases wide
        · obtain ⟨-, hho⟩ := hA rfl rfl
          simp only [hPart, Bool.false_eq_true, ite_false]
          exact bytesAt_frame hf (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact hL.stk_scr (by omega_using [hho]) (by omega_using [hD])) (by omega_using [hQ])
        · obtain ⟨_, _, hdn⟩ := hW rfl rfl
          simp only [hPart, ite_true]
          refine congrArg (List.replicate (Q - D) 0 ++ ·) ?_
          exact bytesAt_frame hf (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (hL.gc.sub_left (Region.sub_prefix hdn)).sub_right (Offset.sub_base _ (by omega_arith))) (by omega_arith)
    cases wide
    · obtain ⟨hQ64, hho⟩ := hA rfl rfl
      simp only [Bool.false_eq_true, ite_false, hPart]
      exact tail_ok hL hcu hdi' hsi' hD h8 hQ64 hho hq
    · obtain ⟨hQD, hQ66, hdn⟩ := hW rfl rfl
      simp only [ite_true, hPart]
      exact tailW_ok hL hcu hdi' hsi' ((hg _ (by decide)).trans (hdx rfl)) hD hD8 hQD hQ66 hq hdn

end VG.Proof.Ecdsa.Rfc6979.X86_64
