module

import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Copy
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Hmac
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Regs
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! ### `Ecdsa.Rfc6979.Arm.Msg`, which only this module used -/

section

/-!
# Deterministic ECDSA on 32-bit ARM: the messages of steps d, f and h.3

`b`, and `‖ d ‖ h` if `full`, at `scratch + 2256` (`msg_ok`): the byte `b`
(`strb_ok`), then the private key (`r5`) and `h`, from the frame at `fHo`,
each copied to `scratch` (`r11`) by `copyBytes` (`copyB_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.X25519.Arm (wp_mov wp_strb wp_str op2_imm)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

theorem ptr_r0 : ∀ r ∈ ptrRegs, r ≠ .r0 := by decide

theorem byte_self (m : Mem) (a : Addr) (v : BitVec 8) : m.writeW a v a = v := by
  simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero, Nat.reduceDiv,
    Nat.zero_lt_one, ite_true]
  exact BitVec.extractLsb'_eq_self

theorem setw8 (b : Nat) : (BitVec.ofNat 32 b).setWidth 8 = BitVec.ofNat 8 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

/-- The byte `b` stored at `scratch + o`, through `r0`. -/
theorem strb_raw (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {b o : Nat} (hb : b < 2) (ho : o < 4096) :
    WP isa (.block [.mov .r0 (.imm (BitVec.ofNat 32 b)), .strb .r0 .r11 o]) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧
      u'.mem = u.mem.writeW (State.addr L.scr + BitVec.ofNat 64 o) (BitVec.ofNat 8 b) :=
  wp_movS (op2_imm (by rcases (by omega_arith : b = 0 ∨ b = 1) with rfl | rfl <;> decide)) fun s₁ u₁ =>
    wp_strb (a := State.addr L.scr + BitVec.ofNat 64 o) ho
      (by rw [u₁.other _ (by decide), hc.r11]; exact scrA hL (by omega_arith))
      (by rw [u₁.wr]; exact hc.inScrW (by omega_arith)) fun s₂ m₂ =>
      WP.block_nil ⟨by rw [m₂.rd, u₁.rd], by rw [m₂.wr, u₁.wr], by rw [m₂.sp, u₁.sp],
        fun r hr => by rw [m₂.gpr, u₁.other _ hr], by rw [m₂.mem, u₁.mem, u₁.gpr, setw8]⟩

/-- The same, with `Ctx` kept. -/
theorem strb_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {b o : Nat} (hb : b < 2) (ho : o + 1 ≤ 8192)
    (ho' : o < 4096) :
    WP isa (.block [.mov .r0 (.imm (BitVec.ofNat 32 b)), .strb .r0 .r11 o]) u fun u' =>
      Ctx L g m₀ u' ∧ (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧
      u'.mem = u.mem.writeW (State.addr L.scr + BitVec.ofNat 64 o) (BitVec.ofNat 8 b) :=
  WP.mono_syms (strb_raw hL hc hb ho') fun u' ⟨hrd, hwr, hsp, hg, hm⟩ sy => by
    have hf : Frame [⟨State.addr L.scr + BitVec.ofNat 64 o, 1⟩] u.mem u'.mem := by
      rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    exact ⟨hc.keep hL hrd hwr hsp (fun r hr => hg r (ptr_r0 r hr)) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L ho) sy, hg, hm⟩

/-- `Q` bytes copied to `scratch + d` by `copyBytes`, with `Ctx` kept. -/
theorem copyB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : BitVec 32} (hs : u.gpr src = S)
    (hsr : src ≠ .r0) {so d Q : Nat} (h4 : 4 ≤ Q) (hd : d + Q ≤ 4096) (hso : so + Q ≤ 4096)
    (hsn : S.toNat + so + Q ≤ 2 ^ 32)
    (hr : ∀ j, j + 4 ≤ Q → InRegions (u.rd ++ u.wr) (State.addr S + BitVec.ofNat 64 (so + j)) 4)
    (hsep : Region.Disjoint ⟨State.addr S + BitVec.ofNat 64 so, Q⟩ ⟨State.addr L.scr + BitVec.ofNat 64 d, Q⟩) :
    WP isa (.block (Cfg.copyBytes Q src so .r11 d)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧ Frame [⟨State.addr L.scr + BitVec.ofNat 64 d, Q⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (State.addr L.scr + BitVec.ofNat 64 d) Q =
        Spec.Sha256.bytesAt u.mem (State.addr S + BitVec.ofNat 64 so) Q := by
  have := hL.nc
  refine WP.mono_syms (copyBytes_ok (by decide) hsr hsep hsn (by omega_arith) hso hd h4 hs hc.r11 hr
    fun j hj => hc.inScrW (by omega_arith))
    fun u' ⟨hrd, hwr, hsp, hg, hf, hb⟩ sy => ?_
  exact ⟨hc.keep hL hrd hwr hsp (fun r hr => hg r (ptr_r0 r hr)) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega_arith)) sy,
    hg, hf, hb⟩

/-- `h` in the messages of steps d and f: `Q` bytes of the frame at `fHo`. -/
abbrev hOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 (24 + (cfgOf P).fHo)) P.Q

theorem fHo_le (P : RfcHash) : (cfgOf P).fHo ≤ 192 := by
  simp only [Cfg.fHo]; split <;> simp [fX, fH]

theorem fHo_ge (P : RfcHash) : 128 ≤ (cfgOf P).fHo := by
  simp only [Cfg.fHo]; split <;> simp [fX, fH]

/-- The message `b` (`‖ d ‖ h` if `full`, `Q` bytes each) at `scratch + 2256`. -/
theorem msg_ok (hL : L.Ok) (hq : P.Q ≤ L.q) {t : State} (hc : Ctx L g m₀ t) {b : Nat} (hb : b < 2) (full : Bool) :
    WP isa (.block ((cfgOf P).msg b full)) t fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧
      Frame [⟨msgA L, 2 * P.Q + 1⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (msgA L) (if full then 1 + 2 * P.Q else 1) =
        [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem (State.addr L.d) P.Q ++ hOf P L t.mem else []) := by
  have nc := hL.nc
  have nd := hL.nd
  have hQ := P.wsizes
  have hho := fHo_le P
  have hho' := fHo_ge P
  simp only [Cfg.msg]
  rw [WP.block_append_iff]
  refine WP.mono (strb_ok hL hc hb (o := sMsg) (by decide) (by decide)) fun u ⟨hcu, hg, hm⟩ => ?_
  simp only [sMsg] at hm
  have hf : Frame [⟨State.addr L.scr + BitVec.ofNat 64 2256, 1⟩] t.mem u.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
      have := Region.contains_self (State.addr L.scr + BitVec.ofNat 64 2256) 1
      exact this)
  have hb₁ : Spec.Sha256.bytesAt u.mem (msgA L) 1 = [BitVec.ofNat 8 b] := by
    show [u.mem (State.addr L.scr + BitVec.ofNat 64 2256 + BitVec.ofNat 64 0)] = _
    rw [BitVec.add_zero, hm, byte_self]
  cases full
  · simp only [Bool.false_eq_true, ite_false, List.append_nil]
    refine WP.block_nil ⟨hcu, hg _ (by decide), hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩, hb₁⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by omega_arith)
  · simp only [ite_true]
    have hcl : (cfgOf P).len = P.Q := rfl
    rw [hcl, WP.block_append_iff]
    refine WP.mono (copyB_ok hL hcu (src := .r5) hcu.r5 (by decide) (so := 0) (d := sMsg + 1) (Q := P.Q)
      (by anums) (by simp only [sMsg]; anums) (by anums) (by anums)
      (fun j hj => by rw [Nat.zero_add]; exact hcu.inD (by omega_arith) (by anums))
      ((hL.dc.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by simp only [sMsg]; anums))))
      fun u₁ ⟨hc₁, hg₁, hf₁, hd₁⟩ => ?_
    refine WP.mono (copyB_ok hL hc₁ (src := .r8) hc₁.r8 (by decide) (so := (cfgOf P).fHo)
      (d := sMsg + 1 + P.Q) (Q := P.Q)
      (by anums) (by simp only [sMsg]; anums) (by anums)
      (by have := hL.nB; have := L.sp.isLt; have := hL.na
          have hfp : L.fp.toNat = L.sp.toNat - 512 := VG.Arm.FrameStack.sub_toNat' (by omega_arith)
          rw [hfp]; anums)
      (fun j hj => by rw [hL.fpA0, Offset.add_add]; exact hc₁.inFr (by omega_arith) (by anums))
      (by rw [hL.fpA0, Offset.add_add]; exact hL.stk_scr (by anums) (by simp only [sMsg]; anums)))
      fun u₂ ⟨hc₂, hg₂, hf₂, hd₂⟩ => ?_
    refine ⟨hc₂, by rw [hg₂ _ (by decide), hg₁ _ (by decide), hg _ (by decide)], ?_, ?_⟩
    · refine ((hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hf₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).trans
        (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      all_goals simp only [List.mem_singleton] at hr; subst hr
      · exact Region.sub_prefix (by omega_arith)
      · exact Offset.sub _ (by simp only [sMsg]; omega_arith) (by simp only [sMsg]; omega_arith)
      · exact Offset.sub _ (by simp only [sMsg]; omega_arith) (by simp only [sMsg]; omega_arith)
    · simp only [sMsg] at hf₁ hd₁ hf₂ hd₂
      rw [show 1 + 2 * P.Q = 1 + (P.Q + P.Q) by omega_arith, Proof.Hmac.Common.bytesAt_add _ _ 1,
        Proof.Hmac.Common.bytesAt_add _ _ P.Q P.Q, Offset.add_add, Offset.add_add]
      have hfd : Spec.Sha256.bytesAt u.mem (State.addr L.d) P.Q = Spec.Sha256.bytesAt t.mem (State.addr L.d) P.Q :=
        bytesAt_frame hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by omega_arith))) (by omega_arith)
      have hfh : hOf P L u.mem = hOf P L t.mem :=
        bytesAt_frame hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hL.stk_scr (by anums) (by omega_arith)) (by omega_arith)
      have hfh₁ : hOf P L u₁.mem = hOf P L u.mem :=
        bytesAt_frame hf₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hL.stk_scr (by anums) (by anums)) (by omega_arith)
      have e1 : Spec.Sha256.bytesAt u₂.mem (msgA L) 1 = [BitVec.ofNat 8 b] := by
        rw [bytesAt_frame hf₂ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith),
          bytesAt_frame hf₁ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith), hb₁]
      have e2 : Spec.Sha256.bytesAt u₂.mem (State.addr L.scr + BitVec.ofNat 64 (2256 + 1)) P.Q =
          Spec.Sha256.bytesAt t.mem (State.addr L.d) P.Q := by
        rw [bytesAt_frame hf₂ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith),
          hd₁, BitVec.add_zero, hfd]
      have e3 : Spec.Sha256.bytesAt u₂.mem (State.addr L.scr + BitVec.ofNat 64 (2256 + 1 + P.Q)) P.Q =
          hOf P L t.mem := by
        rw [hd₂, hL.fpA0, Offset.add_add, ← hfh, ← hfh₁]
      rw [e1, e2, e3]

end VG.Proof.Ecdsa.Rfc6979.Arm

end

end


/-!
# Deterministic ECDSA on 32-bit ARM: the steps on `K` and `V`

`V = HMAC_K(V)` (`hmacV_ok`); `K = HMAC_K(V ‖ m)` for the message `m` at
`scratch + 2256` (`hmacK_ok`); `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then
`V = HMAC_K(V)` (`rekeyFull_ok`, steps d–g); and `K = HMAC_K(V ‖ 0x00)`,
then `V = HMAC_K(V)` (`rekey_ok`, step h.3). Each changes only `scratch`,
the stack below the frame, and `K` and `V`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- `K` and `V`, of the hash function's output length, in the frame. -/
abbrev kOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte := keyOf P L m

/-- What the steps change: `scratch`, the stack below the frame, `K` and `V`. -/
abbrev KVW {dn : Nat} (L : Lay dn) : List Region := [L.SCR, ⟨L.B, 152⟩]

theorem kvw_of {rs : List Region} (h : ∀ r ∈ rs, Region.Sub r L.SCR ∨ Region.Sub r ⟨L.B, 152⟩) :
    ∀ r ∈ rs, ∃ r' ∈ KVW L, Region.Sub r r' := fun r hr => by
  rcases h r hr with h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨⟨L.B, 152⟩, by simp, h⟩

theorem done_kvw {dst : Nat} (h : dst + P.F.H.D ≤ 128) :
    ∀ r ∈ [WK L, ⟨L.B, 24⟩, ⟨L.B + BitVec.ofNat 64 (24 + dst), P.F.H.D⟩], ∃ r' ∈ KVW L, Region.Sub r r' :=
  kvw_of fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (Region.sub_prefix (by omega_arith))
    · exact .inr (Region.sub_prefix (by omega_arith))
    · exact .inr (Offset.sub_base _ (by omega_arith))

theorem st_disj (hL : L.Ok) {d n : Nat} (hd : 24 ≤ d) (hn : d + n ≤ 536) :
    ∀ r ∈ [WK L, ⟨L.B, 24⟩], Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (hL.kc.sub_left (Offset.sub_base _ hn)).sub_right (Region.sub_prefix (by omega_arith))
  · exact Offset.disjoint_base _ hd (by omega_arith)

theorem kv_disj {d : Nat} (hd : d = 0 ∨ d = 64) (hL : L.Ok) :
    ∀ r ∈ [WK L, ⟨L.B, 24⟩, ⟨L.B + BitVec.ofNat 64 (24 + (64 - d)), P.F.H.D⟩],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 (24 + d), P.F.H.D⟩ r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hL.kc.sub_left (Offset.sub_base _ (by rcases hd with rfl | rfl <;> anums))).sub_right
      (Region.sub_prefix (by omega_arith))
  · exact Offset.disjoint_base _ (by omega_arith) (by rcases hd with rfl | rfl <;> anums)
  · exact Offset.disjoint _ (by rcases hd with rfl | rfl <;> anums) (by rcases hd with rfl | rfl <;> anums)
      (by rcases hd with rfl | rfl <;> anums)

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).hmacV t fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem) := by
  unfold Cfg.hmacV
  refine WP.seq (WP.mono (init_step hL hT hc) fun u hu => ?_)
  refine WP.seq (WP.mono (updV_step hL hT hu) fun w hw => ?_)
  have hv : vOf P L u.mem = vOf P L t.mem :=
    bytesAt_frame hu.frame (st_disj hL (by decide) (by anums)) (by anums)
  rw [hv] at hw
  refine WP.mono (fin_step (len := 0) (dst := 64) hL hT hw (by simp [vOf, Spec.Sha256.bytesAt]) (by decide)
    (by anums) (by decide) (by decide)) fun t' h => ?_
  exact ⟨h.ctx, h.r9, h.frame.sub (done_kvw (by anums)),
    bytesAt_frame (p := L.B + BitVec.ofNat 64 (24 + 0)) h.frame (kv_disj (d := 0) (.inl rfl) hL) (by anums),
    h.mac⟩

/-- `K = HMAC_K(V ‖ m)`, for the message `m` of `len` bytes at `scratch + 2256`. -/
theorem hmacK_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {len : Nat} (hlen : len ≤ 256)
    (hle : encodable (BitVec.ofNat 32 len) = true) :
    WP isa ((cfgOf P).hmacK len) t fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧
      Frame (KVW L) t.mem t'.mem ∧ vOf P L t'.mem = vOf P L t.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ Spec.Sha256.bytesAt t.mem (msgA L) len) := by
  unfold Cfg.hmacK
  refine WP.seq (WP.mono (init_step hL hT hc) fun u hu => ?_)
  refine WP.seq (WP.mono (updV_step hL hT hu) fun w hw => ?_)
  have hv : vOf P L u.mem = vOf P L t.mem :=
    bytesAt_frame hu.frame (st_disj hL (by decide) (by anums)) (by anums)
  rw [hv] at hw
  refine WP.seq (WP.mono (updM_step hL hT hw (by simp [vOf, Spec.Sha256.bytesAt]) hlen) fun w' hw' => ?_)
  have hm : Spec.Sha256.bytesAt w.mem (msgA L) len = Spec.Sha256.bytesAt t.mem (msgA L) len := by
    have hf := hw.frame
    refine bytesAt_frame hf (fun r hr => ?_) (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · exact (low_scr hL (by omega_arith) (by omega_arith)).symm
  rw [hm] at hw'
  refine WP.mono (fin_step (len := len) (dst := 0) hL hT hw' (by simp [vOf, Spec.Sha256.bytesAt]) hlen
    (by anums) (by decide) hle) fun t' h => ?_
  exact ⟨h.ctx, h.r9, h.frame.sub (done_kvw (by anums)),
    bytesAt_frame (p := L.B + BitVec.ofNat 64 (24 + 64)) h.frame (kv_disj (d := 64) (.inr rfl) hL) (by anums),
    h.mac⟩

/-- `K = HMAC_K(V ‖ b (‖ d ‖ h))`, then `V = HMAC_K(V)`. -/
theorem rekey_gen (hL : L.Ok) (hT : TabL P L) (hq : P.Q ≤ L.q) {t : State} (hc : Ctx L g m₀ t) {b : Nat}
    (hb : b < 2) (full : Bool) {len : Nat} (hlen : len = if full then 1 + 2 * P.Q else 1) :
    WP isa (.seq (.block ((cfgOf P).msg b full)) (.seq ((cfgOf P).hmacK len) (cfgOf P).hmacV)) t
      fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧ Frame (KVW L) t.mem t'.mem ∧
        kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem (State.addr L.d) P.Q ++ hOf P L t.mem else [])) ∧
        vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) := by
  refine WP.seq (WP.mono (msg_ok hL hq hc hb full) fun u ⟨hcu, h9u, hfu, hbu⟩ => ?_)
  have hl : len ≤ 256 := by cases full <;> simp only [hlen, Bool.false_eq_true, ite_true, ite_false] <;> anums
  have he : encodable (BitVec.ofNat 32 len) = true := encodable_lt (by
    cases full <;> simp only [hlen, Bool.false_eq_true, ite_true, ite_false] <;> anums)
  refine WP.seq (WP.mono (hmacK_ok hL hT hcu (len := len) hl he) fun w ⟨hcw, h9w, hfw, hvw, hkw⟩ => ?_)
  refine WP.mono (hmacV_ok hL hT hcw) fun t' ⟨hc', h9', hf', hk', hv'⟩ => ⟨hc', by rw [h9', h9w, h9u], ?_, ?_, ?_⟩
  · exact ((hfu.sub (kvw_of fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inl (Offset.sub_base _ (by anums)))).trans hfw).trans hf'
  · have hku : kOf P L u.mem = kOf P L t.mem := bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by anums) (by anums)) (by anums)
    have hvu : vOf P L u.mem = vOf P L t.mem := bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by anums) (by anums)) (by anums)
    rw [hk', hkw, hku, hvu, List.append_assoc, hlen, hbu]
  · have hvu : vOf P L u.mem = vOf P L t.mem := bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by anums) (by anums)) (by anums)
    rw [hv', hk', hvw, hvu]

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
theorem rekeyFull_ok (hL : L.Ok) (hT : TabL P L) (hq : P.Q ≤ L.q) {t : State} (hc : Ctx L g m₀ t) {b : Nat}
    (hb : b < 2) :
    WP isa ((cfgOf P).rekeyFull b) t fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧
      Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
        (Spec.Sha256.bytesAt t.mem (State.addr L.d) P.Q ++ hOf P L t.mem)) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) :=
  rekey_gen hL hT hq hc hb true (len := 1 + 2 * (cfgOf P).len) rfl

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
theorem rekey_ok (hL : L.Ok) (hT : TabL P L) (hq : P.Q ≤ L.q) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).rekey t fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [0]) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) :=
  WP.mono (rekey_gen hL hT hq hc (b := 0) (by decide) false (len := 1) rfl) fun _ h => ⟨h.1, h.2.1, h.2.2.1, by
    rw [h.2.2.2.1]; simp, h.2.2.2.2⟩

end VG.Proof.Ecdsa.Rfc6979.Arm
